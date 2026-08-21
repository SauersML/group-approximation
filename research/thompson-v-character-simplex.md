---
rg: 2
id: thompson-v-character-simplex
kind: claim
title: Thompson V has only the trivial and regular extreme characters
distinct_from:
  rcc-carrier-character-face-compression: that reduces a relative-commutant problem to factorial characters of an HNN carrier; this classifies the entire character simplex of the bare simple Higman--Thompson group V.
  thompson-v-not-lef: that uses finite presentability and simplicity to rule out finite local models; this is a finite-factor representation theorem and controls arbitrary tracial characters.
  partial-center-thompson-schur-return: that uses Thompson V as address geometry for a Clifford multiplicity return; this statement has no tape, packet, or central phase.
---

For the classical Thompson group `V=G_(2,1)`, the only indecomposable
(equivalently extreme normalized) characters are

```text
tau_triv(g)=1,
tau_reg(g)=1 if g=1 and 0 otherwise.
```

Consequently every tracial state on `C*(V)` is uniquely of the form

```text
tau_t=t tau_reg+(1-t)tau_triv,       0<=t<=1.
```

This is a citation import from Dudko--Medynets, not a new classification
proved in this repository.
