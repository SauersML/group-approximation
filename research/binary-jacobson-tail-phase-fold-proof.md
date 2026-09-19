---
rg: 2
id: binary-jacobson-tail-phase-fold-proof
kind: route
title: Expand the phase-corrected two-branch fold on each tail sign
target: binary-jacobson-tail-phase-cannot-correct-closing-fold
requires:
  - binary-jacobson-closing-root-folds-head-two-to-one
  - binary-jacobson-head-sector-has-native-two-qubit-packet
---

All roots in `(JTP2)` commute with `c=x_13(ST)`.  The root `b=x_12(1)`
also commutes with `c`, while it exchanges `E_-` and `E_+`.  Thus a spectral
phase `phi=phi(c)` commutes with every displayed operator.  Since `R` and
`Rb` have the identical final projection and orthogonal cross ranges,

```text
T_phi T_phi^*
 =(1/2)(RR^*+Rb phi phi^* bR^*)=F.                     (1)
```

The same expansion with the tail cut inserted gives

```text
T_phi P_epsilon T_phi^*=R E_-P_epsilon R^*=F_epsilon.   (2)
```

The sign swap `bE_-b=E_+` commutes with `P_epsilon`, so the two intersections
`E_-P_epsilon,E_+P_epsilon` have equal rank and sum to `P_epsilon`.
The partial isometry `R` is isometric on the first one, proving `(JTP5)`.

The relative branch calculation is

```text
b Z_0 b=x_13(1)Z_0=x_13(Q)x_13(ST)Z_0.                 (3)
```

On `P_epsilon`, the last two root factors in `(3)` act as `-epsilon`.
The mixed terms in

```text
(1/2)R(1+b phi)Z_0(1+phi^*b)R^*                       (4)
```

vanish because `Z_0` preserves `E_-` whereas `b` exchanges the two `Y`
signs.  The two diagonal terms in `(4)` are therefore

```text
(1/2)(1-epsilon)RZ_0R^*,                               (5)
```

and the phase has cancelled completely.  The roots `X_1,Z_1` commute with
`b` and preserve `E_-`; the same expansion gives the last two equations of
`(JTP6)`.

For completeness, `X_0` commutes with `b` but exchanges `E_-` and `E_+`.
If `phi|_(P_epsilon)=zeta_epsilon`, the surviving cross terms give

```text
T_phi X_0 T_phi^*
 =Re(zeta_epsilon) R bX_0R^*.                           (6)
```

For a self-adjoint phase `zeta_epsilon in {+1,-1}`, this is a self-adjoint
unitary in the `F_epsilon` corner.  It commutes with the last Pauli pair.
On `F_+`, equation `(5)` makes the other first-pair entry zero, so the folded
algebra is a quotient of `C^*(C_2) tensor M_2`, hence of
`M_2 directSum M_2`, and Amitsur--Levitzki gives `s_4=0`.

On `F_-`, equation `(5)` gives `RZ_0R^*`.  The commutator of this operator
with the unitary in `(6)` is the transported head sign `-F_-`; the last
pair has the same negative center and cross-commutes with the first.  Thus
the two Pauli pairs generate `M_4 tensor I` on every nonzero reducing
summand.  This proves `(JTP7)` and the phase-correction no-go.
