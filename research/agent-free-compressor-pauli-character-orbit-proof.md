---
rg: 2
id: agent-free-compressor-pauli-character-orbit-proof
kind: route
title: Put all four relative Pauli coefficients in one Fourier label
target: agent-free-compressor-pauli-orbit-misses-child
requires:
  - schur-packet-child-square-is-pauli-transverse
---

Use the nondegenerate trace pairing on the matrix algebra `S`.  A functional
`chi_M` vanishes on `S_A` exactly when the identity coefficient of `M` in its
relative Pauli expansion is zero.  To see this, write

```text
M=C_I tensor I+C_X tensor X+C_Y tensor Y+C_Z tensor Z.
```

Then, for `a in M_D(k)`,

```text
Tr(M(a tensor I))=2 Tr(C_I a).                          (1)
```

Nondegeneracy of the `M_D(k)` trace pairing and odd characteristic prove the
criterion.

For `(PCO4)` all four coefficients equal `I_D`.  Multiplication on either
side by a relative Pauli matrix permutes these four coefficients and changes
only nonzero scalar signs.  Multiplication by a baseline packet element
multiplies every coefficient by an invertible `D`-by-`D` matrix.  Thus the
identity coefficient remains nonzero throughout the complete `B_f` orbit,
proving the second part of `(PCO3)`.  Equation `(1)` at `a=I_D` gives
`Tr(MP)=2D!=0`, proving the first part after choosing `psi`.

Finally let `H=ell^2(O)` and let the additive root group act diagonally by
the characters in `O`.  Let `B_f` permute the standard basis through its
action on `O`.  This is an exact representation of the finite semidirect
root/actor window and its character multiplicity function is the indicator
of `O`.  It has the two masses asserted after `(PCO5)`, so any positive
constant in `(PCO5)` is impossible.
