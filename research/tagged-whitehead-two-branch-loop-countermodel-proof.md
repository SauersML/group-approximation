---
rg: 2
id: tagged-whitehead-two-branch-loop-countermodel-proof
kind: route
title: Realize the tagged return loop by three Pauli factors and tensor swaps
target: tagged-whitehead-two-branch-loop-has-a-three-qubit-marked-model
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

On

```text
H=(C^2) tensor (C^2) tensor (C^2)
```

let `X_r,Z_r` denote the Pauli `X,Z` on tensor factor `r`, and put

```text
C_r=X_r,                  H_r=Z_r,
J=-I_H,                   K=Z_3,
W_12=SWAP_(1,2),          W_23=SWAP_(2,3).             (1)
```

Pauli anticommutation gives `[C_r,H_r]=-I_H=J`, while operators on
different factors commute.  The tag `K` commutes with `C_1,H_1,C_2,H_2`;
for either of the first two branch columns, replacing `H_r` by `H_rK`
therefore leaves its diagonal commutator equal to `J` and its crossed
commutators equal to one.  (A tag on the third branch may instead be placed
on a harmless extra tensor factor; it is not used in the tested two-branch
loop.)

Tensor swap conjugates `(X_r,Z_r)` to the corresponding pair on the swapped
factor.  Moreover `W_12` fixes the third factor and hence commutes with
`K=Z_3`.  Thus `(TWL2)` holds.  Adjacent tensor swaps are involutions and
satisfy the Coxeter braid, proving `(TWL3)`.  Finally

```text
W_12[C_1,H_1K]W_12^(-1)=[C_2,H_2K]=J,                 (2)
```

so the tagged mixed loop `(TWL4)` is exactly one.  All proposed local
discrepancy words therefore vanish although
the nontrivial spectral projection of `J` is the identity of `H`.

If these rows implied `(BAC1)`, zero right-hand side would give four
operators in `B(H)` with both inverse defects and the completeness defect
zero.  The binary case of
`atomic-leavitt-gap-on-nonzero-matrix-corner` forbids this on a nonzero
finite matrix corner.  Therefore the local tagged Whitehead return table
cannot imply the three-row compiler estimate.
