---
rg: 2
id: dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
kind: claim
title: Hadamard answer reduction preserves affine safety except at the PCPP view, where it can fail exactly
distinct_from:
  culf-mastel-rstar-reduction-is-support-blind: that observes that the fixed-language reduction states no support theorem; this audits the preceding Dong--Fu--Natarajan--Qin--Xu--Yao completeness transformation and gives an explicit perfect-strategy counterexample to affine-safety preservation.
  fano-cap-witness-sections-force-source-affine-safety: that gives the affine-safety condition needed by a later cap-valued witness section; this identifies the unique test family in the published source protocol where that condition can be lost.
---

**ESTABLISHED TRANSFORMATION AUDIT AND COUNTEREXAMPLE.**  Consider the
Hadamard-code answer reduction `V -> V_AR` of Dong--Fu--Natarajan--Qin--
Xu--Yao, instantiated with the perfect-completeness strategy in their
Theorem 35.  Every accepting relation belonging to a consistency cross-check
or to the Hadamard subset/code tester is affine over `F_2`.  Consequently the
positive answer-pair support of the honest strategy is affine-safe in each of
those tests:

```text
Aff(S_r) subseteq C_r.                                  (DAR1)
```

The only unresolved relations are the `Verify` tests.  For a fixed original
question pair `(x_0,x_1)` and PCPP random view

```text
r=(I_0,I_1,J),                                           (DAR2)
```

the honest support is obtained by restricting the Hadamard encodings of an
original positive joint answer `(y_0,y_1)` and of one perfect PCPP witness
`pi_(y_0,y_1)` to the sampled view (and to the extra dummy coordinates).
Thus affine safety at `r` is exactly the assertion that the PCPP predicate at
`r` accepts the affine hull of these restricted codeword/witness views.  The
published completeness theorem states no such closure property.

In fact this property is **not preserved by the answer-reduction
transformation**, even for a fixed finite perfect real commuting symmetric
EPR strategy.  Let an input verifier have one question pair, accept exactly
the three equal answer pairs

```text
(e_1,e_1), (e_2,e_2), (e_3,e_3),
e_1=100, e_2=010, e_3=001,                              (DAR3)
```

and use a real diagonal three-outcome PVM of ranks `2,1,1` on each half of
two EPR pairs.  All three pairs have positive mass.  For their perfect PCPP proofs
`pi_1,pi_2,pi_3`, put

```text
y_*=e_1+e_2+e_3=111,
pi_*=pi_1+pi_2+pi_3.                                    (DAR4)
```

The pair `(y_*,y_*)` is invalid and its two Hadamard codewords are at relative
distance `1/2` from every valid encoded pair.  Since the PCPP proximity
parameter is at most `1/4` and its soundness is strictly below one, some
random view `r` rejects the queried restriction of the proof `pi_*`.  But
Hadamard encoding and coordinate restriction are linear, so that rejected
view is the xor of the three accepted honest views at `r`.  An xor of three
points is an affine combination over `F_2`; hence

```text
Aff(S_r) not subseteq C_r.                              (DAR5)
```

Therefore neither Theorem 35 nor the subsequent Culf--Mastel use of its
perfect oracularizable strategy can imply affine safety from perfectness,
realness, EPR symmetry, or oracularizability alone.  This does **not** prove
that the particular HALT strategy chosen in Theorem 36 is affine-unsafe.  It
reduces that source-specific question to the finitely many PCPP view images
in `(DAR2)`; the primary papers do not compute those supports or prove their
affine closure.
