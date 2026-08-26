---
rg: 2
id: fused-authenticated-cross-returns-retain-s3-square-gauge
kind: claim
title: The fused authenticated cross returns retain an S3-square gauge
artifacts:
  - research/fused-authenticated-cross-return-gauge-proof.md
distinct_from:
  cross-whitehead-sandwiches-branch-roots-into-signed-normalizer: that classifies every one-word-plus-root return branchwise; this fuses the complementary returned coefficients `q_0,q_1` on the same output root and tests the complete resulting occurrence table.
  stabilized-cross-braid-has-s3-square-gauge-fence: that fuses complementary three-coordinate braid packets whose last two coefficient products retain `p+r`; this forms the literal completeness sum `q_0+q_1=1` after two individually authenticated `K_i` returns.
  mixed-completeness-braid-retains-s3-square-gauge: that forms completeness inside one aggregate braid containing factors of `K_0`; this uses the separately authenticated full-Gram returns through both `K_0` and `K_1`.
---

**ESTABLISHED FUSED-RETURN FENCE.**  Fix `k` in `{6,9}` and define

```text
R_0=x_(8,k)(r),        R_1=x_(8,k)(p),
O_0=x_(7,k)(q_0),      O_1=x_(7,k)(q_1),
N=x_(7,k)(1).                                            (FAR1)
```

The positive individual-return classification gives the literal identities

```text
K_0R_0K_0=O_0,        K_1R_1K_1=O_1.                    (FAR2)
```

Because the two outputs are occurrences in the same root subgroup,
completeness is now used after both authenticated returns:

```text
[O_0,O_1]=1,          O_0O_1=N,                         (FAR3)
```

by `q_0+q_1=1`.  The input occurrences similarly commute and fuse to
`R_0R_1=x_(8,k)(p+r)`.

The complete displayed return-and-fusion table still has an exact finite
reservoir model.  In `S_3 times S_3`, choose reflections
`a=(1 2)`, `b=(2 3)`, and `c=(1 3)`, so `cac=b`, and set

```text
d_0=(c,1),       d_1=(1,c),
a_0=(a,1),       a_1=(1,a),
b_0=(b,1),       b_1=(1,b).                            (FAR4)
```

Assign `d_i` to `K_i`, `a_i` to `R_i`, and `b_i` to `O_i`.  Then

```text
d_0a_0d_0=b_0,       d_1a_1d_1=b_1,                   (FAR5)
a_0a_1=(a,a),         b_0b_1=(b,b).                    (FAR6)
```

Thus all conjugation, cross-commutation, input-fusion, and output-fusion
rows hold exactly.  But the constant output `N` carries the nontrivial
diagonal gauge `(b,b)`; `(FAR3)` does not make it the identity and does not
identify either branch gauge separately.  For `k=6` or `9`, this is exactly
an allowed constant signed-normalizer occurrence, so the old external
normalizer gauge has been reconstructed rather than cancelled.

This is a scoped reservoir model of the displayed ordinary occurrence
table, not a finite representation of EL20.  Closing ESB now requires an
additional native occurrence that types the fused constant output gauge or
compares one returned `b_i` individually with a selector factor.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
fused-authenticated-cross-return-gauge-proof
