---
rg: 2
id: agent-first-hit-one-schur-two-cell-is-regular-absorbed
kind: claim
title: One Schur predicate holonomy cell is conditionally exact but is absorbed by marked regular multiplicity
distinct_from:
  schur-packet-flips-realize-predicate-cocycle: that constructs the predicate-dependent projective commutator and records its parity consequence; this tests it as the missing two-cell in a fresh-copy first-hit tree and constructs the exact marked countermodel plus the sharp HS remainder repair.
  fixed-d8-holonomy-has-no-determinant-density: that treats an abstract fixed projective system; this keeps exact BCS completeness visible and shows directly that the finite packet semidirect product restores the stationary regular model.
  agent-first-hit-finite-fresh-tree-has-marked-matrix-model: that applies when there is no relation among edge intertwiners; this audits the first proposed two-cell beyond that hypothesis and shows that it can be absorbed into a larger finite vertex packet.
---

**ESTABLISHED.**  Let `B_f` be the finite Schur predicate packet and let
`alpha_P,alpha_Q` be the commuting involutive automorphisms from
`schur-packet-flips-realize-predicate-cocycle`.  Form the ordinary finite
presentation

```text
G_f=<B_f,u,v |
      u b u^(-1)=alpha_P(b),
      v b v^(-1)=alpha_Q(b)       (b in B_f),
      [u,v]=1>.                                          (SRA1)
```

This is a valid predicate-sensitive two-cell.  On every allowed selector
sector the two packet implementers act linearly on the allowed orbit sum and
may be chosen commuting.  On a forbidden invariant simple `T_x`, their packet
parts `P_x,Q_x` anticommute.  Thus on

```text
T_x tensor C^m                                          (SRA2)
```

the stable letters have Schur form

```text
rho(u)=Q_x tensor S,        rho(v)=P_x tensor T,         (SRA3)
```

and `(SRA1)` is equivalent to

```text
S T=-T S.                                               (SRA4)
```

Consequently `2|m`.  If the perfect BCS trace has no forbidden atom, no
forbidden `T_x` occurs and this constraint is vacuous.  The cell therefore
has exactly the requested exact-completeness behavior.

It does **not** destroy the marked regular stationary model.  Since
`alpha_P,alpha_Q` are commuting involutions, the finite semidirect product

```text
F_f=B_f rtimes (C_2 x C_2)                              (SRA5)
```

is a quotient of `(SRA1)`.  Its negative regular corner is an exact
finite-dimensional representation with the common central mark `J=-I`.
Equivalently, on `l^2(B_f)` the two automorphisms are implemented by their
commuting permutation unitaries.  The restriction of this model to `B_f`
is the marked regular representation, so every forbidden simple occurs with
positive multiplicity and `(SRA4)` is automatically absorbed by its external
multiplicity space.

There is also no normalized-Hilbert--Schmidt obstruction hidden in odd
multiplicity.  For odd `m`, use exact Pauli anticommuting blocks on
`C^(m-1)` and arbitrary scalar unitaries on the last coordinate.  All
covariance relations remain exact and the commutation relator is wrong only
on `T_x tensor C`.  Conditional on `(SRA2)`,

```text
||[rho(u),rho(v)]-I||_2^2=4/m.                         (SRA6)
```

Thus the defect tends to zero while the forbidden sector occupies the whole
isotypic carrier.  External amplification by two makes the cell exact.

More generally, a fixed finite family of independent binary Schur squares of
cocycle rank `2r` forces only

```text
2^r | m.                                               (SRA7)
```

The corresponding finite Clifford/semidirect packet has an exact marked
regular model.  If `m` is not divisible by `2^r`, delete fewer than `2^r`
multiplicity coordinates and obtain total fixed-relator squared HS error
`O_r(2^r/m)`.  Hence every fixed-depth fresh tree of these cells still has
zero-defect marked matrix models, regardless of the positive forbidden mass.

The result identifies the exact limitation of one holonomy relation.  It
can convert nonlinear forbidden membership into a projective phase, but a
fixed projective phase constrains only external multiplicity divisibility.
To force a rank floor one needs cocycle rank growing with the current model,
a positive density of bounded-multiplicity fibers, or a genuine proper-corner
return.  None is supplied by one fixed two-cell.

DERIVATION
agent-first-hit-one-schur-two-cell-is-regular-absorbed via agent-first-hit-schur-two-cell-regular-model-proof

