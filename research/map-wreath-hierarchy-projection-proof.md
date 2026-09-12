---
rg: 2
id: map-wreath-hierarchy-projection-proof
kind: route
title: Project a minimally almost periodic image first to the base and then to each lamp
target: map-groups-cannot-enter-the-rf-wreath-hierarchy
requires:
  - recursive-wreath-libraries-have-stably-finite-group-algebras
  - binary-leavitt-unit-group-is-minimally-almost-periodic
---

First, every homomorphism f:M->K into a residually finite group is trivial.
If f(m)!=1, a finite quotient of K separates it from the identity. Composing
with the faithful unitary regular representation of that finite group gives
a nontrivial finite-dimensional unitary representation of M, a contradiction.

Induct on the hierarchy depth. Suppose all maps from M into every group in
C_n are trivial, and consider f:M->A wr_X G with A,G in C_n. Composing
with the quotient onto G gives a trivial map. Thus the image lies in the
restricted direct product of the lamps A. Projection to each coordinate
A is a homomorphism and is trivial by induction. Every coordinate of f(m)
is therefore the identity, so f is trivial.

A map to a subgroup of a finite product of these wreath groups is also
trivial: compose the inclusion with every product projection. This proves
the induction step for C_(n+1), and hence the assertion for C_fin.

If K is residually C_fin and f:M->K has a nonidentity value, a separating
homomorphism K->L with L in C_fin contradicts the preceding result. This
proves the residual-closure statement. The established minimal almost
periodicity of Q gives the stated specialization, independently of any
nonsoficity announcement.

For an increasing union K=union_i K_i with K_i in C_fin, a homomorphism
from a finitely generated M has its generating image in one common stage;
therefore the whole map factors through that stage and is trivial. This
uses injective inclusions. The argument does not apply to a general
directed colimit with noninjective structure maps.
