---
rg: 2
id: finite-packet-triangle-repair-is-ideal-block-choi-feasibility
kind: claim
title: Finite-packet triangular ucp repair is exactly an ideal-block Choi-cone intersection
distinct_from:
  fd-representation-packets-never-obstruct-ucp-sections: that constructs some packetwise repair with unrestricted ideal depth; this gives a necessary-and-sufficient feasibility test for repairs constrained to one prescribed finite reservoir and removes the forced quotient block from the variables.
  finite-reservoir-compactness-lifts-ucp-repairs: that compactifies a fixed reservoir serving every packet; this identifies the exact finite-dimensional Choi slice that the reservoir must meet for each packet before compactness can be invoked.
  property-t-alone-cannot-correct-tracial-choi-lifts: that rules out a universal property-T correction of negative coordinate Choi directions; this is a positive exact reduction specific to the minimally almost periodic Kac--Moody quotient and locates all Kraus freedom in the relator-ideal block.
  tree-face-balance-pays-stinespring-loss-or-word-distance: that gives a norm obstruction obeyed by an eventual exact ucp balance; this is a packetwise necessary-and-sufficient convex feasibility condition and does not assume values are near group words.
---

**ESTABLISHED.**  Use the explicit simple Kac--Moody triangle and write

```text
A=C^*(G_0),       I=ker(q:A->>Q=C^*(Lambda)),
E subset Q a finite-dimensional operator system,
t:E->A a unital self-adjoint linear section,
L subset I a prescribed finite-dimensional self-adjoint reservoir. (IBC1)
```

Let `rho:A->M_D` be any finite-dimensional representation (including the
direct sum of an arbitrary finite packet), and put

```text
B=rho(A),       J=rho(I),       z=1_J in B.                (IBC2)
```

Thus `z` is the central support projection of the ideal `J` in the
finite-dimensional algebra `B`.  Let `epsilon:Q->C` be the augmentation
character.  Since `Lambda` is infinite, finitely generated and simple, every
finite-dimensional unitary representation of `Lambda` is trivial.  Hence

```text
B/J=C(1-z),
(1-z)rho(t(x))=epsilon(x)(1-z)       for x in E.           (IBC3)
```

Regard `J` as a unital C-star algebra with unit `z`, and write
`UCP_z(E,J)` for the relative-unital slice of the finite-dimensional
matrix-ordered Choi cone: the completely positive maps `theta:E->J` satisfying
`theta(1)=z`.  Then the following are equivalent:

```text
(a) some d:E->L makes rho o (t+d):E->B ucp;

(b) [z rho o t + rho_* L_sa(E,L)] intersect UCP_z(E,J)
    is nonempty.                                           (IBC4)
```

Here `L_sa(E,L)` denotes the real vector space of self-adjoint linear maps and
`rho_* L_sa(E,L)={rho o d:d in L_sa(E,L)}`.  All variables in `(IBC4)` are
finite-dimensional.  In particular, for a fixed relator reservoir `L_W`, the
open packetwise assertion `(RR2)` is exactly the statement that `(IBC4)` is
feasible for the direct sum of every finite packet.

Equivalently, `(IBC4)` fails exactly when there is a real linear functional
`F` on the self-adjoint map space `L_sa(E,J)` such that

```text
F(rho o d)=0                 for every d in L_sa(E,L),
F(z rho o t)>sup{F(theta):theta in UCP_z(E,J)},            (IBC6)
```

after reversing the sign of `F` if necessary.  Thus failure of a proposed
finite reservoir has a finite-dimensional dual Choi witness which annihilates
every allowed relator coefficient and strictly separates the raw ideal-block
lift from all relative-unital cp maps.

Proof: `ideal-block-choi-feasibility-proof`.

**Constructive meaning.**  The quotient block is not part of the problem: it
is forced to be the scalar map `x |-> epsilon(x)(1-z)`.  Every genuinely
non-inner Kraus degree of freedom lives in the ideal block `J`, and the only
remaining task is to place a relative-unital cp map `theta:E->J` in the
finite affine space

```text
z rho o t + rho_* L_sa(E,L).                               (IBC5)
```

This is strictly sharper than asking for arbitrary ideal preimages basis by
basis.  It exposes the coupled positivity condition that a finite-reservoir
construction must preserve across all three faces.  It does not prove those
intersections are nonempty for one uniform `L_W`.

**Exhausting-depth endpoint.**  For an increasing sequence of relator
reservoirs dense in `I`,
`exhausting-ideal-reservoirs-have-lift-or-quotient-separator` explains exactly
how the dual certificates may be passed to a limit.  One must first pull
`F_m` back to the fixed map space by `s |-> F_m(z_m rho_m o s)`.  A uniform
normalized gap then gives a quotient-level separator; without that
conditioning the signed Choi certificates have no positive-vector or
low-spectrum limit.  The invariant global reservoir-to-ucp distances either
tend to zero, which already gives an exact local lift, or stay positive, which
produces the quotient separator directly.

DERIVATION
ideal-block-choi-feasibility-proof
