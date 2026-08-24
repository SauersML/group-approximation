---
rg: 2
id: binary-leavitt-has-no-purely-singular-free-near-representation
kind: claim
title: The binary Leavitt unit group admits no purely singular essentially free near representation
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that asks the original normalized-Hilbert--Schmidt approximation question; this is its equivalent state-theoretic negative form after all normal state mass has been eliminated.
  near-representation-amenability-dichotomy: that asks a general Kazhdan near-representation rigidity question; this is the single explicit singular-state instance needed for the first nonsofic group.
---

**OPEN.**  Prove that for

```text
Q=L_(F_2)(1,2)^x
```

there are no Hilbert space `H`, purely singular state `phi` on `B(H)`, and
`phi`-near representation `pi:Q -> U(H)` satisfying

```text
phi(pi(g))=0                    for every g != 1.        (BLSG1)
```

By `binary-leavitt-hyperlinear-iff-purely-singular-near-representation`, this
is **exactly** the negative side of the Leavitt hyperlinearity fork, with no
normal-state slack left.

The live input is the singularity.  The ordinary Bekka--Valette proof cannot
apply property (T) to `Ad pi`, because `pi` is only multiplicative in the
state seminorm; `near-representation-amenability-dichotomy` records that
operator-norm mismatch.  The stronger established property `(TT)/T` of `Q`
is therefore relevant only if one can manufacture a genuine unitary
representation and a quasi-cocycle from the singular near-state without
assuming the desired exactification.
