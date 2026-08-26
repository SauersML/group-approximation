---
rg: 2
id: binary-leavitt-atomic-morita-return
kind: claim
title: Return one binary Leavitt coefficient cell to the marked root spectral atom
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that asks for exact depth-one and depth-two matrix-unit packets with one identity and a vanishing support-leakage row; this asks instead for four corner coefficient operators satisfying only two diagonal inverse rows and one completeness row.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: that is a normalized-Hilbert--Schmidt decoder for an odd-characteristic affine-Leavitt group and needs positive relative carrier mass; this is the operator-norm binary-Leavitt decoder and rank one is enough.
  corona-coefficient-module-decoder: that reconstructs a coherent unital action of the whole coefficient ring on one finitely generated projective corona module; this reconstructs one binary cell on one prescribed finite-coordinate atom and allows the coefficient window to vary with the coordinate.
artifacts:
  - research/binary-leavitt-atomic-return-via-three-row-compiler.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.** Work in the fixed finite binary-Leavitt Steinberg presentation
of

```text
Delta=St_20(L_(F_2)(1,2))
```

with the distinguished involutive root

```text
z=x_13(q),                         q=s_1t_1.
```

For every sufficiently accurate operator-norm presentation model `U`, round
`z(U)` to an involution and prescribe its nontrivial spectral projection

```text
p_U=(1-z_round(U))/2.
```

Prove a dimension-independent modulus `eta(delta)->0` such that, whenever
`p_U!=0`, there are bounded operators

```text
s_0,s_1,t_0,t_1 in p_U M_d(C) p_U
```

satisfying

```text
||t_i s_i-p_U||_op <= eta(delta),              i=0,1,
||s_0t_0+s_1t_1-p_U||_op <= eta(delta).                (BLAMR)
```

The carrier is prescribed before the coefficient operators are chosen, so
the zero-carrier shortcut is unavailable.  No lower bound on its normalized
rank is requested, the off-diagonal rows are omitted, and different finite
coefficient windows may be used at different coordinates.

Establishing this claim and applying
`atomic-morita-return-kills-finite-order-mf-mark` kills `z`; the established
root-saturation calculation then gives total MF radical.

## Attempts

The direct typed-packet attack fails: `rectangular-escape`,
`literal-prefix-three-root-swap-retains-typed-carriers`, and
`typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier` give exact
finite models of every separately typed packet while keeping the source and
target identities on different reservoirs.  A universal group-algebra
selector also fails by
`fixed-group-algebra-polynomials-cannot-supply-atomic-return`: on the regular
marked corner, arbitrary compressed root-word polynomials have total
three-row defect at least one.  Finally, the existing normalized-Hilbert--Schmidt
ledgers cannot be upgraded: a leakage row can have operator norm one on a
vanishing-rank carrier while its ambient normalized-HS norm tends to zero.

The live attack is `binary-leavitt-three-row-atomic-compiler`: derive the
three rows from finitely many prototype discrepancies at a
coordinate-dependent, losslessly conjugated address.

The authenticated support-idempotent returns do not by themselves furnish
such prototypes.  `support-return-odd-loops-do-not-imply-atomic-return`
retains both literal odd native factorizations, their transported Pauli-chart
covariances, chart intersection and native braid in one exact finite marked
model.  Applying the atomic gap on its nonzero marked atom proves that no
three-row output with a vanishing modulus follows from that finite menu.  A
live compiler must add a relation coupling coefficient completeness to the
prescribed atom, rather than only recombine `Z_i,H_i,W_i,J_i`.
