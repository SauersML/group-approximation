---
rg: 2
id: separate-occurrence-arrows-do-not-lock-pauli-gauge
kind: claim
title: Separate occurrence arrows do not lock a Pauli multiplicity gauge
artifacts:
  - research/separate-occurrence-pauli-gauge-countermodel-proof.md
distinct_from:
  zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner: that asks for active and identity-label occurrences on one positive corner; this proves that two independently transported occurrences, even exact on the whole active atom, do not identify the original pair jointly.
  pauli-gauge-word-retains-and-cocycle: that rules out producing a pure gauge word by fixed label dressing; this is an elementary joint-conjugacy obstruction after identity-label actors have already been supplied.
  leavitt-crossed-gram-pauli-charge-has-sectorwise-escape: that varies a gauge pair by selector sector; this keeps one active atom and shows that independent occurrence frames alone lose its commutator.
---

**ESTABLISHED SEPARATE-ARROW FIREWALL.**  The displayed conditions
`(AIM1)--(AIM2)` in
`zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner` do not by
themselves make the active multiplicity commutator trivial when the two
occurrence identifications `W_A,W_B` are independent.

On a positive active selector atom `E_11`, take a label factor `L` and a
gauge qubit `G` with Pauli involutions `X_g,Z_g`. Set

```text
A_11=I_L tensor X_g,             B_11=I_L tensor Z_g,
A^o =B^o=I_L tensor Z_g.                              (SAF1)
```

Let `H_g` be the Hadamard involution, so `H_g X_g H_g=Z_g`, and put

```text
R=E_11,             W_A=I_L tensor H_g,       W_B=I.  (SAF2)
```

Extend the two arrows block diagonally outside `E_11`. Then they preserve
the selector atom rather than transporting it elsewhere, and

```text
R(A^o-W_A A_11 W_A^*)=0,
R(B^o-W_B B_11 W_B^*)=0,
R([A^o,B^o]-1)=0.                                    (SAF3)
```

Thus `(AIM1)--(AIM2)` hold with defect zero and the best possible mass
constant `c=1`. Nevertheless,

```text
[A_11,B_11]=I_L tensor (-I_G),                         (SAF4)
```

so the original gauge commutator is maximally nontrivial on every nonzero
piece of `R`.

All actors and arrows lie in a finite Clifford group, and tensoring
spectators preserves the example. Therefore the remaining mixed-occurrence
gate must contain a **joint-frame** condition: for example, one common
occurrence arrow for both actors, or a mixed Gram relation controlling
`W_A^*W_B` on `R`. Two separate operator occurrences plus commutation of
their targets carry no information about the commutator of the original
pair.
