---
rg: 2
id: middle-index-heisenberg-center-chain-fence-proof
kind: route
title: Compute the six root-coordinate ejections under the chained arms
target: middle-index-heisenberg-packet-is-not-center-chain-invariant
requires:
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
---

For each `m`, the arm `A_m` in `(MIC1)` ends at the same middle coordinate
at which `Y_m` starts.  The Steinberg relation gives

```text
[x_(r,k_m)(a_m),x_(k_m,3)(b_m)]=x_(r,3)(a_mb_m).
```

Similarly `X_m` ends where `B_m` starts, so

```text
[x_(1,k_m)(a_m),x_(k_m,s)(b_m)]=x_(1,s)(a_mb_m).
```

Substituting `a_mb_m=q` and the outer indices from `(MIC1)` proves
`(MIC2)--(MIC3)`.  In the elementary image, the original packet has
off-diagonal support only in the seven positions

```text
(1,7),(1,8),(1,9),(7,3),(8,3),(9,3),(1,3).
```

The six output positions in `(MIC2)--(MIC3)` are absent, and their
coefficient `q` is nonzero.  Hence none of the corresponding conjugates
lies in the packet.

For `u_1=B_2A_1`, conjugation of `Y_1` by `A_1` creates `x_43(q)`.
The factor `B_2=x_84(b_2)` can only add a root in position `(8,3)` by
composing with `(4,3)`; it cannot remove the `(4,3)` coordinate.  For
`u_2=B_3A_2A_1`, neither `A_2=x_58(a_2)` nor `B_3=x_95(b_3)` has a
Steinberg incidence that removes `(4,3)`.  Thus the ejection remains in
both full mixed words.

Finally, imposing normalization while retaining the named arms and duals
would require all six ejection coefficients to be zero.  Each is
`a_mb_m=q`, contradicting the nonzero marked center relation.  This is the
claimed exact finite-packet fence; it does not assert that every possible
larger packet orbit is infinite.
