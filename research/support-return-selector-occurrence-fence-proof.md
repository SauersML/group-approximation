---
rg: 2
id: support-return-selector-occurrence-fence-proof
kind: route
title: Classify the label and source types of the support-return odd-loop occurrences
target: support-return-selector-occurrence-fence
requires:
  - support-return-gives-gauged-native-loop
  - support-return-charts-meet-in-two-pauli-pairs
  - quarter-whiteheads-lack-unequal-source-conjugacy
---

Equation `(SRL7)` proves that `J_1,J_2` normalize the fixed same-center
three-pair packet, that `W_1,W_2` do not, and that each `Khat_i` acts only
on the transported chart `E_i=W_iEW_i`.  Equation `(SRL6)` identifies the
action of `Khat_i` on `E_i` with the conjugate of the native action of
`J_i`.  By `(SCW4)`, each native action is an adjacent two-qubit swap, whose
negative eigenspace in the eight-dimensional label has dimension two.
This proves items 1--3 and the three quarter-fraction assertions.

Equations `(SCI2)--(SCI5)` prove that the transported charts meet in
exactly two Pauli pairs and that `S=W_1W_2` centralizes this intersection.
Thus its label action on the common subpacket is the identity.  A
three-qubit rank-one reflection cannot be recovered after deleting the
third Pauli pair, which proves item 4.

Finally `(QWS5)--(QWS7)` show that the center-chain Hecke ranks are
occurrence-untyped analytic supports and that every common native-Whitehead
reduction collapses the two Hecke target maps.  Hence no named source row
supplies either conjugacy in `(SRO2)`.

For the finite gauge witness, apply independent central sign twists to
`W_1,W_2` and the corresponding inverse twists to the definitions of
`Khat_1,Khat_2`.  Because the signs are central involutions, they cancel in
`W_iKhat_iW_i`; the native words and braid are fixed.  Their product remains
free on the label-trivial intersection.  This realizes every displayed
support-return and chart-intersection row while leaving the missing
selector identification unconstrained.
