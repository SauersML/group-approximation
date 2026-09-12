---
rg: 2
id: transition-equivariance-proof
kind: route
title: The raw swap routes all four named translation commutators exactly
target: transition-equivariance
requires: []
artifacts:
  - GroupApproximation/Leavitt/RawSwapCompressors.lean
  - notes/TRUE_RAW_SWAP_FULL_BRANCH_ROUTING.md
  - notes/TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md
---

The transition between the comb compressor `u` and the raw compressor
`w u` is the raw swap `w = rawInvolutionWord L`.  The required covariance
therefore reduces to conjugation by this one group element.

Write the three core coordinates as `0,1,2` and the routed coordinate as
`3`.  The fixed middle root is `H = x_12(1)`.  Since `w` only uses the
`0` and `3` coordinates, it commutes with `H` exactly.  (Equivalently this
is immediate from `rawInvolutionWord_val`: the `1,2` block is the identity.)
For the two coefficient families, `RawSwapCompressors.lean` already proves
all four operand identities, with no approximation:

```text
w x_01(s0 a) w^-1 = x_01(s0 a),
w x_01(s1 a) w^-1 = x_31(-a),
w x_20(b t0) w^-1 = x_20(b t0),
w x_20(b t1) w^-1 = x_23(-b).
```

The first and third are exactly
`rawInvolutionWord_commutes_firstBranchRow` and
`rawInvolutionWord_commutes_firstBranchColumn`.  The second and fourth are
the conjugation forms of `rawInvolutionWord_mul_lastRow` and
`rawInvolutionWord_mul_lastColumn`; multiply their stated mul-past identities
on the right by `w^-1`.

Now use the group identity

```text
w [x,y] w^-1 = [w x w^-1, w y w^-1].
```

Because `w H w^-1 = H`, the four identities above give the four literal
middle-root translation covariances:

```text
w [x_01(s0 a), H] w^-1 = [x_01(s0 a), H],
w [x_01(s1 a), H] w^-1 = [x_31(-a), H],
w [H, x_20(b t0)] w^-1 = [H, x_20(b t0)],
w [H, x_20(b t1)] w^-1 = [H, x_23(-b)].
```

These are precisely the branch-0 fixed and branch-1 routed versions demanded
in the remaining literal audit of
`TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md`: the branch-1 target
translations are written in last-row/last-column coordinates before applying
(ETM21).  The minus signs are harmless and are part of the already recorded
raw routing convention; negation is a bijection of the additive coefficient
packet/orbit and does not change the translation family.

Thus every one-sided map `a |-> a t_i` and `b |-> s_j b`, for `i,j in {0,1}`,
has the required covariance under the **same physical raw/comb transition**.
No extra Pauli, spectral, or gauge input is needed.  The separate
`same-orbit-closure` claim remains essential: this closes equivariance, not the
rectangular-escape obstruction.
