---
rg: 2
id: two-qubit-clifford-closes-transverse-m2-chord-proof
kind: route
title: Conjugate the target Pauli by controlled gates in two transverse bases
target: two-qubit-clifford-closes-transverse-m2-chord
requires:
  - full-root-separators-force-uniform-chord
---

The Pauli commutation rules give `[Z_1,Z_1Z_2]=0` and
`[X_1,X_1Z_2]=0`.  Since `Z_1` and `X_1` generate `M_2(C)` on the first
qubit, `(TQC2)` follows.

The standard CNOT conjugation rules are

```text
U_0 Z_1 U_0^*=Z_1,             U_0 Z_2 U_0^*=Z_1Z_2.  (TQP1)
```

The gate is an involution, so the second identity also gives
`U_0(Z_1Z_2)U_0^*=Z_2`.  This proves `(TQC4)` for `i=0`.
Conjugating `(TQP1)` on the first qubit by the Hadamard, which exchanges
`Z_1` and `X_1`, gives

```text
U_1 X_1 U_1^*=X_1,             U_1 Z_2 U_1^*=X_1Z_2.  (TQP2)
```

Again `U_1` is an involution, proving `(TQC4)` for `i=1`.

The finite Clifford group contains the Pauli subgroup and the gates in
`(TQC3)`.  Any invariant subspace for its defining representation is in
particular invariant under the two-qubit Pauli group, whose linear span is
all of `M_4(C)`; hence the representation is irreducible and `(TQC5)` is its
primitive group-algebra block.

Finally the common relative commutant in `(TQC2)` is
`I_2 tensor M_2(C)`.  It has no nontrivial projection before the second
factor is added, while `(TQC6)` is rank one in that factor.  For either
rank-one separator atom `e` on the first qubit, `ep` has rank one inside the
rank-two space `e(C^2 tensor C^2)`, so its conditional fraction is `1/2`.
The extension-independent uniformity and the asserted sharp scaling boundary
then follow from `full-root-separators-force-uniform-chord`.
