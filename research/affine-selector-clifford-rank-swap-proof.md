---
rg: 2
id: affine-selector-clifford-rank-swap-proof
kind: route
title: Fourier-rotate the reset Pauli and apply the complementary controlled pairs
target: affine-selector-clifford-rank-swap-balanced
requires:
  - affine-selector-clifford-residual-packet
  - four-point-gauge-orbit-has-balanced-derived-rank-swap
---

The five-qubit selector Pauli symplectic space has dimension ten.  The four
commuting semantic Paulis
`T_a,Z_(ell_2),Z_(ell_3),Z_(ell_4)` form a Lagrangian subspace of the
semantic eight-dimensional symplectic space.  The dummy frame `X_0,Z_0` is
orthogonal to it and has pairing one.  Witt extension sends this full frame
to the standard frame displayed in `(ACR1)`.  The finite selector Clifford
group implements that map.  In that basis the operators
`(GRS1)` are controlled-X and
controlled-Z gates, hence Clifford involutions.  Their commutator computation
is exactly `four-point-gauge-rank-swap-proof`.  Conjugation back proves
`(ACR2)` with `T_a` itself on the right side.

The three semantic linear forms annihilating `a` commute with `T_a`; together
they form a maximal commuting rank-four semantic Pauli subgroup.  Each joint
character therefore cuts the four semantic qubits to dimension one.  None of
these four operators uses the dummy qubit, so that qubit remains dimension
two and carries the active pair.  Tensoring with the residual spin gives
`(ACR4)`.  On the old side, fixing the four original semantic `Z_i` also
leaves exactly that dummy qubit, so both restrictions are `2 rho_15`.

This dimension check also shows why the nineteen-qubit version is invalid:
without the dummy qubit a full semantic character leaves dimension one, even
though fixing only the reset sign misleadingly leaves several free selector
dimensions.
