---
rg: 2
id: qutrit-psync3-tensor-closure-obstruction
kind: claim
title: Tensor closure refutes complement-flexible qutrit projector synchronization in one nontrivial central sector
distinct_from:
  qutrit-fixed-space-projector-synchronizer: that proposed the now-refuted PSync_3 endpoint.
---

**ESTABLISHED NO-GO.**  No ordinary-group gadget can satisfy both clauses of
`qutrit-fixed-space-projector-synchronizer` as stated.

Let `omega` be a primitive third root of unity.  Complement-flexible perfect
completeness applied to the following four scalar interface pairs gives four
exact finite-dimensional representations in the sector `J=omega I`:

```text
(U_1,V_1)=(omega I,   omega I),
(U_2,V_2)=(omega I,   omega I),
(U_3,V_3)=(omega^2 I, omega I),
(U_4,V_4)=(omega^2 I, omega I).
```

Every pair is admissible because both fixed-space projectors are zero.  Take
the tensor product of the four exact representations.  Ordinary group
relations remain exact under tensor product, while

```text
J = omega^4 I = omega I,
u = omega^(1+1+2+2) I = I,
v = omega^4 I = omega I.
```

Thus the tensor product is again an exact representation in the soundness
sector, but

```text
Pi_0(u)=I,       Pi_0(v)=0.
```

The right side of `(PS3-1)` is zero and the left side is one.  This is a
contradiction.  The argument is unchanged by any fixed matrix amplification
allowed in the completeness clause.

The obstruction is categorical: the visible exact relation

```text
Pi_0(U)=Pi_0(V)
```

is not closed under tensor products within the `J=omega` sector after four
copies, whereas the restrictions of exact ordinary-group representations in
that sector necessarily are.  Hence adding noncommuting auxiliaries, a finite
packet, a cyclic sum-of-squares certificate, or more relators cannot repair
the proposed endpoint without weakening its exact completeness or changing
the carrier/sector architecture.
