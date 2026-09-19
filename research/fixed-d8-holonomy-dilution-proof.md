---
rg: 2
id: fixed-d8-holonomy-dilution-proof
kind: route
title: Fill all complete Clifford blocks and confine every defect to the remainder
target: fixed-d8-holonomy-has-no-determinant-density
requires: []
---

Take the block direct sum in `(FDH1)`.  Every relator is exactly the identity
on the `ql`-dimensional summand.  On the remaining `s`-dimensional summand it
is the difference of two unitaries, whose operator norm is at most `2`.
Therefore its unnormalized Hilbert--Schmidt norm is at most `2 sqrt(s)`;
division by `sqrt(m)` proves `(FDH2)`.

For `(FDH3)`, both the squared Hilbert--Schmidt norm and the ambient dimension
gain the factor `dim(T)=2`.  The factors cancel after normalization.  Direct
sums of finitely many projective orientation packets have one fixed common
exact dimension (their product suffices), so the same remainder argument
applies to all of them simultaneously.

