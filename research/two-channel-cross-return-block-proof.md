---
rg: 2
id: two-channel-cross-return-block-proof
kind: route
title: Multiply the only possible two stable rank-two support patterns
target: two-distinct-rank-two-channels-cannot-factor-cross-return
requires:
  - first-cross-whitehead-has-no-alternative-low-depth-return
---

Let `P_A,P_B` be the two coordinate support pairs.  If
`u in P_A minus ({7,8} union P_B)`, then `B` fixes the `u` row and column,
so a nontrivial `A` entry incident to `u` cannot disappear from `AB`.
The same statement with `A,B` reversed shows that the external coordinates
in the two pairs must agree.  Since the pairs are distinct and each must
meet the target pair, after exchanging `7,8` their only possible pattern is
`(TCR2)`.

Literal block multiplication gives `(TCR4)--(TCR5)`.  For `AB` to be
supported only on `(7,8)`, its first row and column off the diagonal must
vanish.  Regardless of how those equations are solved in the Leavitt ring,
the `(8,7)` entry is already the literal zero displayed in `(TCR4)`.  For
`BA`, the literal `(7,8)` entry is zero instead.  Thus every surviving
two-channel product is triangular on the target pair.

By `first-cross-whitehead-has-no-alternative-low-depth-return`, a signed
normalizer supported on `(7,8)` is either `1` or `x_78(1)`.  Left
multiplication of `(TCR1)` by those two blocks gives `(TCR7)`.  Direct
multiplication by the native block

```text
J_1=[[q_1,y_1],[x_1,1+e_00]]
```

gives `(y_1,r)` in both cases, as computed in the same-pair return proof.
The reduced Leavitt matrix units `p,r,y_1,q_0` make all displayed entries
nonzero.  Hence the triangular support invariant excludes every target in
`(TCR6)` and `(TCR8)`.
