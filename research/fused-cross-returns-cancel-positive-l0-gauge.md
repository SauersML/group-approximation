---
rg: 2
id: fused-cross-returns-cancel-positive-l0-gauge
kind: claim
title: The fused authenticated cross returns cancel their positive L0 output gauge
artifacts:
  - research/fused-cross-return-positive-l0-cancellation-proof.md
distinct_from:
  cross-whitehead-sandwiches-branch-roots-into-signed-normalizer: that classifies every one-word-plus-root return branchwise; this fuses the complementary returned coefficients `q_0,q_1` on the same output root and tests the complete resulting occurrence table.
  stabilized-cross-braid-has-s3-square-gauge-fence: that fuses complementary three-coordinate braid packets in a truncated occurrence table; this uses the already typed positive signed-`L_0` occurrence of the fused constant output.
  mixed-completeness-braid-retains-s3-square-gauge: that forms completeness inside one aggregate braid containing factors of `K_0`; this uses the separately authenticated full-Gram returns through both `K_0` and `K_1`.
---

**ESTABLISHED POSITIVE GAUGE CANCELLATION.**  Fix `k` in `{6,9}` and define

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

Let `Q=e_(L_0,lambda_0)` be the signed Hecke projection in any unitary
representation.  Each `O_i` normalizes the signed pair, hence preserves
`Q`.  Write its restriction to `QH` as `b_i`.  Characteristic two makes
every elementary root in `(FAR1)` an involution, so

```text
b_0^2=b_1^2=1.                                         (FAR4)
```

The fused constant root is not external.  In source-to-target notation it
is `k->7`, and both possibilities

```text
6->7,        9->7                                      (FAR5)
```

are positive-character generators of `L_0` in `(ERN1)`.  Therefore
`rho(N)Q=Q`.  Restricting `O_0O_1=N` to `QH` gives

```text
b_0b_1=1,       hence b_0=b_1.                         (FAR6)
```

Thus completeness cancels the fused output gauge and identifies the two
branch output actions on the signed Hecke carrier.  It does **not** make
either individual `b_i` trivial, identify it with a selector-row factor,
or identify either repeated `K_i` occurrence with a native Whitehead
factor.  The former `S_3 times S_3` assignment with
`b_0b_1=(b,b) ne 1` models only the truncated rows `(FAR2)--(FAR3)` and
cannot extend to the established positive `L_0` typing `(FAR5)`.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
fused-cross-return-positive-l0-cancellation-proof
