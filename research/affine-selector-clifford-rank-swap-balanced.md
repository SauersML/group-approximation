---
rg: 2
id: affine-selector-clifford-rank-swap-balanced
kind: claim
title: An inert selector qubit supplies the equal-scale full-character reset spin
artifacts:
  - experiments/affine_selector_dummy_full_character_audit.py
  - experiments/affine-selector-dummy-full-character.json
distinct_from:
  four-point-gauge-orbit-has-balanced-derived-rank-swap: that gives the abstract two-sign rank arithmetic; this uses an inert dummy selector qubit to compute the restriction after all four semantic selector signs, rather than only the reset sign, are fixed.
---

Fix a nonzero reset direction `a`, and choose a basis
`ell_2,ell_3,ell_4` of the three-dimensional annihilator of `a`.  The
dummy Pauli pair commutes with `T_a` and with all three semantic signs.  A
selector-only Clifford change of basis sends

```text
T_a -> Z_1,                    X_0,Z_0 -> X_2,Z_2,
Z_(ell_j) -> Z_(j+1),                 2<=j<=4.          (ACR1)
```

In the coordinates `(ACR1)`, use selector qubit two as the auxiliary Pauli
pair and define the two complementary controlled pairs of
`four-point-gauge-orbit-has-balanced-derived-rank-swap`, controlled by the
sign of `Z_1`.  Conjugate them back by the selector Clifford change of basis.
The resulting four ordinary Clifford involutions satisfy

```text
[p_-,q_-]=T_a,
[p_+,q_+]=J T_a,                                      (ACR2)
```

and all cross commutators are trivial.  In particular the actual gauge
translation `T_a` is a commutator, not merely conjugate in the unitary group
to a derived phase.

The rank-fifteen standard residual Paulis commute with these selector-only
operators.  On each `T_a` sign, exactly one pair in `(ACR2)` is a Pauli pair.
The four commuting fresh selectors

```text
T_a, Z_(ell_2), Z_(ell_3), Z_(ell_4)                  (ACR3)
```

fix a one-dimensional subspace of the four semantic selector qubits and leave
the dummy qubit free.  Hence, after a complete fresh semantic character is
fixed, the active controlled pair is precisely the dummy two-dimensional spin
and the restriction is

```text
rho_15 tensor rho_swap = 2 rho_15.                     (ACR4)
```

The old semantic chart has the same restriction by `(ACP4')`: fixing its four
`Z_i` signs leaves the same dummy factor and gives `2 rho_15`.  Thus the old
and fresh full-character restriction matrices agree entry by entry.  If only
the reset sign is fixed, each sign contains eight rank-sixteen blocks; that
coarser count is a consequence, not the edge calculation.

For an arbitrary `J=-1` representation, tensor this calculation with the
common multiplicity space `M` from `(ACP9)`.  Every Clifford extension type
therefore has the same branching matrix; no unselected relevant mode can
absorb the reset current at a different scale.

The extra qubit is not a semantic selector and is never exposed to the BCS.
It is exactly the missing hyperbolic pair, while the four semantic directions
remain available for complete old/fresh character bookkeeping.  Since the
entire construction lies in one fixed finite Clifford group, its restriction
matrix is stable under finite-group exactification with constants independent
of ambient dimension.
