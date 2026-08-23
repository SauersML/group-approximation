---
rg: 2
id: hybrid-rank-router-tensor-closure-obstruction
kind: claim
title: Tensor closure refutes the universal exact hybrid rank router
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
distinct_from:
  qutrit-psync3-tensor-closure-obstruction: that uses four scalar third-root interfaces to refute universal qutrit fixed-space synchronization; this uses three marked binary reflection interfaces and directly contradicts rank conjugacy.
  normal-finite-role-packets-cannot-route-controlled-payloads: that gives an operator-Schmidt obstruction for normal finite packet covariance; this refutation applies to arbitrary auxiliaries and arbitrary ordinary relators.
---

**ESTABLISHED NO-GO.**  No ordinary-group gadget can simultaneously have
the universal routing, soundness, and complement-flexible exact-extension
properties in `hybrid-rank-router-authenticates-affine-overlap-blocks`.

Let `A=1-2P` and `B=1-2Q`.  Universal exact completeness supplies exact
marked representations for the three scalar zero-overlap pairs

```text
(P_1,Q_1)=(1,0),       (A_1,B_1)=(-1,+1),
(P_2,Q_2)=(0,1),       (A_2,B_2)=(+1,-1),
(P_3,Q_3)=(0,0),       (A_3,B_3)=(+1,+1).             (HRT1)
```

Take each representation in the pure negative sector of the marked central
involution `m`, so `m=-I`.  Their tensor product is again an exact
representation of every ordinary group relator and remains in the same
sector because `(-1)^3=-1`.  But the tensor-product interface words are

```text
A=A_1 A_2 A_3=-1,       B=B_1 B_2 B_3=-1.             (HRT2)
```

Zero routing defect in this exact marked representation forces

```text
R=diag(A,B)=-I,          S=diag(AB,1)=I.               (HRT3)
```

The tensor product also satisfies the stable-letter relator exactly, so it
would have a unitary `U` with `URU^*=S`.  Equation `(HRT3)` turns this into
`-I=I`, a contradiction.  Equivalently, the zero right side of the proposed
relator estimate contradicts the rank-conjugacy lower bound

```text
2||PQ||_2^2=2 <= ||URU^*-S||_2=0.                      (HRT4)
```

If no marked order-two sector is part of the statement, the first two
factors already give the contradiction.  Fixed matrix amplifications do not
change it.

Thus the problem is not solved by a larger finite role packet, noncommuting
auxiliaries, nested D8 swaps, or a different finite relator menu.  Any viable
rank-conjugacy compiler must restrict exact completeness to a distinguished
source trace/face which is not closed under these tensor products, or make
the routing inference depend on canonical moments rather than hold in every
exact marked representation.
