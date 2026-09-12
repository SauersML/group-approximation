---
rg: 2
id: affine-selector-clifford-residual-proof
kind: route
title: Evaluate controlled residual Paulis on the selector eigenspaces
target: affine-selector-clifford-residual-packet
requires:
  - fanizza-schur-menu-has-common-codimension-one-residual
---

On a `Z_i` eigenvector with bit `x_i`, the controlled word `CZ_i(w)` is
`Q(w)^(x_i)`.  Multiplying the four controlled words gives `(ACP4)`.

Residual `P(u)` commutes with every selector Pauli and has commutator
`J^(u dot w)` with `Q(w)`.  Its commutator with `CZ_i(w)` is therefore the
selector phase `Z_i^(u dot w)`.  Multiplication over the constant and four
linear terms gives `(ACP5)`.

Conjugation by selector `X_i` complements the control of `CZ_i(w)`.  The
complement-controlled `Q(w)` equals `Q(w)CZ_i(w)`, so a translation by `a`
contributes exactly the residual factor in `(ACP8)`.  It also changes the
selector sign by `(ACP7)`.

Controlled Pauli gates are Clifford gates, and the Clifford group on a fixed
number of qubits is finite modulo scalar phase.  Adjoining the finite scalar
phase group gives the stated finite packet.  The Pauli subgroup has one
irreducible `J=-1` spin representation.  Complete reducibility gives
`(ACP9)` for the restriction of any finite-dimensional Clifford packet
representation, independently of which Clifford extension types occur.

The dummy pair `X_0,Z_0` is absent from every controlled residual word and
commutes with all four semantic `Z_i`.  The joint eigenspace of a full
semantic character therefore has dimension `2*2^15`, and restriction of the
natural packet to the residual group on that eigenspace is exactly
`2 rho_15`.  This proves `(ACP4')`; it is a full-character calculation, not
the coarser calculation obtained by fixing only `T_a`.
