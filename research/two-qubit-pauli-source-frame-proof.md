---
rg: 2
id: two-qubit-pauli-source-frame-proof
kind: route
title: Split the D8 target by one transverse Pauli and compute the forced collapse
target: two-qubit-pauli-frame-covers-common-d8-source
requires:
  - two-letter-dihedral-swap-wordizes-one-gram-row
---

On `P`, relation `zj=yjz` says that `j` exchanges the `z`-eigenspaces, so
`S^*S=Q` and `SS^*=T`.  The transverse generator `a` commutes with `z,j`,
and hence with `S,T,Q`.  Therefore

```text
S^*q_+S+S^*q_-S=S^*TS=Q.
```

The relation `bab=ya` becomes `bab=-a` on `P`; it exchanges `q_+` and
`q_-` and forces equal nonzero ranks in every marked spin summand.

For the row calculation, apply
`two-letter-dihedral-swap-wordizes-one-gram-row` with its first row letter
equal to `z` and its second row letter equal to `d`.  Relative to
`TH direct_sum QH`, the four blocks in `(TLD3)` are

```text
A=T,       C=-Q,       D=-T,       B=2p-Q.             (TPP1)
```

The desired block is

```text
AS-SB=S-S(2p-Q)=2S(Q-p)=2SF,                           (TPP2)
```

while the complementary block vanishes:

```text
CS^*-S^*D=-S^*+S^*=0.                                 (TPP3)
```

The exact square identity `(TLD5)` now gives `(TPF6)`.  Since `TS=S`,
equation `(TPF7)` is immediate.  The rank-one obstruction for a single D8
qubit and the four-dimensional realization of the central product prove the
minimality statement.  Equation `(TPF8)` shows why the selected perfect
sector survives.  If `w=1` is imposed, `(TPF6)` gives `F=0`, proving `(TPF9)`
and the claimed failure of full marked-packet embedding.
