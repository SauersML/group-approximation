---
rg: 2
id: full-hecke-quarter-source-equalizes-selector-ranks
kind: claim
title: Passing both native supports to the full Hecke source equalizes the affine source fractions
artifacts:
  - research/full-hecke-quarter-source-rank-equalization-proof.md
distinct_from:
  b2-b3-pair-full-hecke-four-native-sectors: that proves the positive rank-one-quarter common source inside Q; this records the normalization of the two individual supports on Q and audits what that normalization does to the affine gauge endpoint.
  two-shared-gauge-selector-rows-have-an-affine-rank-obstruction: that gives a contradiction for source fractions one half and one quarter on one normalized carrier; this proves that the full-Hecke restriction changes those fractions to one half and one half, where the same rank equations are compatible.
  same-center-whitehead-native-selector-subcorner-attachment: that asks for the original unequal native rows on a positive typed subcorner; this rules out using the untyped quarter intersection alone as a substitute for that occurrence attachment.
---

**ESTABLISHED NORMALIZATION FENCE.**  Retain the full signed Hecke source

```text
Q=e_(L_0,lambda_0)
```

and the commuting native signs

```text
r=x_58(a_2),                 t=x_69(a_3).
```

The two actual native compression supports on `Q` are

```text
R_1=Q(1+r)/2,                R_2=Q(1+t)/2.             (FQE1)
```

Then

```text
rank(R_1)/rank(Q)=rank(R_2)/rank(Q)=1/2,
rank(R_1R_2)/rank(Q)=1/4.                              (FQE2)
```

Consequently `(FQE2)` cannot be inserted into the two-row affine endpoint
with the original source fractions `(1/2,1/4)`.  After normalizing on `Q`,
the two rows have source fractions `(1/2,1/2)`.  If their controlled label
fractions are still `q_1=1/4` and `q_2=1/8`, the balanced shared gauge

```text
theta=1/2
```

satisfies both rank equations exactly, because

```text
Phi_q(1/2)=1-q+(2q-1)/2=1/2                         (FQE3)
```

for every `q`.  There are exact finite-dimensional reflection rows with
these ranks, a balanced common gauge, and a quarter-rank intersection of
the two source supports.

Thus the `B_2,B_3` calculation supplies a genuine common positive source,
but it does not by itself establish the unequal-row compiler or the full MF
collapse.  A successful continuation must preserve the original
`(1/2,1/4)` source normalization while authenticating the two target
occurrences, or provide a different operator-norm rank obstruction.

No Property `(T)`, canonical trace, computation, literature input, or Lean
compilation is used.

DERIVATION
full-hecke-quarter-source-rank-equalization-proof
