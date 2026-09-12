---
rg: 2
id: center-chain-scalar-gram-polar-cut-returns-moving-atom
kind: claim
title: The center-chain scalar Gram polar cut is exactly the moving atom
invalidates:
  - center-chain-scalar-gram-polar-cut-closes-native
artifacts:
  - research/center-chain-scalar-gram-polar-cut-proof.md
distinct_from:
  center-chain-character-atom-gives-scalar-gram: that proves the exact 1/64 scalar Gram and qualitatively notes that the arms move the atom; this computes the exact arm-overlap and commutator costs and shows that the polar cut cannot replace the atom by a better corner.
  two-transport-cross-gram-has-a-fixed-mass-reducing-corner: that extracts an approximately reducing corner only after the two transports already approximately intertwine one common source packet; here the Gram spectral operator is the atom itself and the required Pauli covariance has a fixed positive defect.
---

Retain the notation of `center-chain-character-atom-gives-scalar-gram`:

```text
H=<C_1,C_2,C_3> ~= UT_4(F_2),       e=e_chi,
S_i=g_i e,                           tau(e)=1/64,
A_1=x_47(a_1),                       A_2=x_58(a_2).       (MPC1)
```

The two selector roots centralize `H`, so `S_i` is a unitary on `e`.  Hence
the cross-Gram operator and its positive square are

```text
G=S_1^*S_2,                 G^*G=e.                       (MPC2)
```

Consequently every nonzero spectral cut of `G^*G` at a threshold in `(0,1]`
is exactly `e`.  In particular the polar-cut conclusion of
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner` cannot select a
smaller subprojection on which the missing Pauli covariance improves.

This failure has a fixed normalized-Hilbert--Schmidt size.  The exact
finite-character intersection calculation gives

```text
tau(e A_1 e A_1^*)=1/256,       ||[e,A_1]||_2^2=3/128,
tau(e A_2 e A_2^*)=1/128,       ||[e,A_2]||_2^2=1/64.     (MPC3)
```

Thus neither arm approximately reduces the scalar-Gram atom, even along
canonical microstates: the displayed constants persist in the regular-trace
limit.  The transport theorem cannot be invoked with these arms as the
shared source packet, because its covariance errors are bounded away from
zero; invoked with the empty packet, or only with operators centralizing
`H`, it returns the tautological cut `e` and supplies no Pauli carrier.

Likewise `two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge`
starts only after both Pauli actions have been placed on one reducing corner.
It cannot turn `(MPC2)` into that missing reduction.  Therefore the exact
`1/64` scalar Gram does not upgrade to the native normalized-HS cross-Gram
claim through any currently established polar-cut or mixed-Pauli theorem.

Finite-packet exactification does not change this conclusion.  Exactifying
the already reducing packet `H` preserves the atom and hence preserves the
two fixed defects in `(MPC3)`.  Enlarging the finite packet to include the
arms removes `e` from its reducing algebra; the finite-packet theorems can
correct an approximate action on a corner already supplied to them, but do
not assert that a positive subprojection of a specified nonreducing
character atom survives the enlargement.  Proving that such a
representation-dependent subprojection survives with fixed mass is a new
intersection/occurrence lemma, not a consequence of finite-dimensional
packet stability.

The sharp missing input is a separate positive-mass subcorner, not determined
by the scalar Gram spectral operator, on which the prescribed arms and the
two actual selector transports satisfy their common covariance relations.

DERIVATION
center-chain-scalar-gram-polar-cut-proof
