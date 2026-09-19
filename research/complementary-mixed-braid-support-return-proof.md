---
rg: 2
id: complementary-mixed-braid-support-return-proof
kind: route
title: Compare the symmetric complementary cells with the actual mixed-braid residual
target: complementary-mixed-braid-returns-support-but-retains-s3
requires:
  - mixed-braid-gauge-cancellation-misses-signed-hecke-targets
  - support-return-gives-gauged-native-loop
---

On the ordered coordinates `(7,9)`, the four symmetric words in `(CMR1)`
have their literal three-elementary definitions.  Expanding first gives

```text
W_79(1,q_1)=[[q_0,q_1],[q_1,q_0]]=W_79(q_1,q_1),
W_79(1,q_0)=[[q_1,q_0],[q_0,q_1]]=W_79(q_0,q_0).      (0)
```

This uses only

```text
q_i^2=q_i,             q_0q_1=q_1q_0=0,
q_0+q_1=1.
```

The two complementary triple products consequently reduce entry by entry
to

```text
W_79(1,q_1) W_79(1,q_0) W_79(1,q_1)=W_79(q_0,q_0),
W_79(1,q_0) W_79(1,q_1) W_79(1,q_0)=W_79(q_1,q_1).
```

The two support blocks are orthogonal, so their product is the full constant
Whitehead `W_79(1,1)`.  The MSI artifact verifies all three identities by
faithful binary-prefix matrix equality and tests every word named in the
claim against all ten generators and the sign character of `L_0`; every
signed-Hecke normalization test is false.

The actual mixed-braid residual has asymmetric first and third root
coefficients:

```text
x_79(q_1)x_97(q_1)x_79(1)
 =[[q_0,1],[q_1,q_0]].                                (1)
```

Thus `(0)` differs from `(1)` in its top-right entry.  The artifacts define
`partial(projection)` with both outer coefficients equal to `ONE`; they
verify `(0)` and the symmetric subgroup closure, not a closure containing
the residual `(1)`.

For `(CMR4)`, breadth-first close the exact seven-by-seven Leavitt matrices
for `A,B,J_1`, reducing coefficients by faithful binary-prefix equality
after every multiplication.  The closure terminates at twelve elements.
Propagate the proposed `A` parity through the Cayley graph; no matrix is
reached with both parities, so it defines a character on the whole closure.
Finally test every one of the twelve matrices against the full ten-generator
signed-`L_0` conjugacy signature, both directly and after multiplication by
`J_1`.  The direct list contains only the identity and the target list only
`J_1`, with even parity in both cases.

For the scoped reservoir model, take adjacent transpositions `a,b` in
`S_3`.  Their two conjugates `aba` and `bab` coincide, and their square is
one, which proves `(CMR3)`.  Tensor the label occurrence table by this
reservoir representation.  Since the support-return word contains `C`
twice, that identity is unchanged.  Thus all named rows remain exact with
the symmetric support-cell spectator nontrivial.
