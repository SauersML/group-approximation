---
rg: 2
id: common-opposite-mark-amalgamation-fence-proof
kind: route
title: Match the marked involution multiplicities in the two finite packets
target: common-opposite-mark-attachment-preserves-full-q-zero-type
requires:
  - full-q-separate-actor-packet-retains-zero-cross-central-block
  - aggregate-morita-common-opposite-return-has-gl3-square-model
---

Let `pi` be the zero-type representation `(SAP5)`.  Since `mF=-F` and
`pi(F)!=0`, the involution `pi(m)` has a negative eigenspace of some
dimension `n>0`.  Write `p` for its positive multiplicity.  Add trivial
one-dimensional representations of `P` until the new positive multiplicity
`p'` satisfies

```text
p'>=n.                                                  (1)
```

Call the resulting representation `pi'`.  In every added trivial summand,

```text
F=(1/|K|) sum_(k in K) chi(k)k
```

acts as zero because `chi` is nontrivial.  Therefore `pi'(F)` is still
nonzero and `pi'(FgF)=0`.

Let `lambda_B` be the left regular representation of the finite group

```text
B=GL_3(F_2) times GL_3(F_2)
```

used in the common-opposite model, and write `N=|B|`.  Its marked
involution `C_1` is nonidentity, so left multiplication by `C_1` partitions
the group basis into two-cycles.  Its positive and negative multiplicities
are both `N/2`.

Take `N` copies of `pi'`.  The shared involution then has multiplicities

```text
(negative,positive)=(nN,p'N).                          (2)
```

On the common-opposite side take `2n` copies of `lambda_B` and
`(p'-n)N` trivial one-dimensional representations of `B`.  The marked
involution there has multiplicities

```text
(2n(N/2), 2n(N/2)+(p'-n)N)=(nN,p'N).                  (3)
```

Equations `(2)--(3)` show that the two restrictions to the shared `C_2` are
unitarily conjugate.  Conjugate the `B` representation by such a unitary
and place it on the same Hilbert space as the amplified `P` representation.
The named common involution is then literally one operator.  Since the two
tables have no other shared occurrence, assigning the remaining generators
from their respective representations gives an exact representation of
their amalgamated presentation.

The `P`-corner relations are unchanged, so `(COM4)` holds.  The `B`-side
relations are unchanged under amplification and unitary conjugacy, so every
binary completeness, returned-child, common-opposite, and Whitehead row in
`(COM3)` holds.  This proves the finite attachment fence.
