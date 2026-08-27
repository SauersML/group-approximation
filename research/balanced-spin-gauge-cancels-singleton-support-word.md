---
rg: 2
id: balanced-spin-gauge-cancels-singleton-support-word
kind: route
title: Balance the controlled fine reflection with one spectator involution and conjugate equal signatures
target: singleton-reflection-has-balanced-eight-dimensional-model
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - odd-selector-row-balances-or-kills-outer-action
  - separate-balanced-hnn-cross-gram-is-typed-overlap
---

Use the unique marked Pauli spin module and its controlled fine reflection.
Tensor the latter with `V=diag(1,-1)`.  Its positive and negative signatures
become `(4,4)`, equal to those of the amplified coarse Pauli reflection, so
unitary conjugacy gives `(SLR3)` and hence `(SLR4)`.  Direct tensor calculation
gives `(SLR5)`.  Trace mismatch excludes multiplicity one, while a trace-zero
involution first occurs in dimension two, proving minimality.  The finite
amalgam construction for the native Whitehead occurrence supplies the stated
extension of the local model.
