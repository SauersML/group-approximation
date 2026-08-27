---
rg: 2
id: affine-selector-clifford-residual-packet
kind: claim
title: One twenty-qubit Clifford packet realizes the affine selector residual pencil with a balanced dummy spin
distinct_from:
  selector-correlated-direct-power-router: that pairs arbitrary truth-table sectors with direct-power coordinates and cancels a balanced HNN word; this uses the affine dependence of the Schur commutator pencil to realize all sectors directly by controlled Clifford operators.
  fanizza-schur-menu-has-common-codimension-one-residual: that finds the common rank-fifteen residual forms; this turns their affine matrix pencil into ordinary words of one finite Clifford group.
---

Let

```text
B(x)=B_0+sum_(i=1)^4 x_i B_i in M_15(F_2)             (ACP1)
```

be the common rank-fifteen residual pencil from
`fanizza-schur-menu-has-common-codimension-one-residual`.  Use four semantic
selector qubits, one dummy selector qubit, and fifteen residual qubits.  Write
`Z_i,X_i`, `1<=i<=4`, for semantic selector Paulis, write `Z_0,X_0` for the
dummy pair, and write `P(u),Q(w)` for residual Paulis, with

```text
[P(u),Q(w)]=J^(u dot w),                 J=-1.          (ACP2)
```

For `w in F_2^15`, let `CZ_i(w)` apply `Q(w)` to the residual register when
selector bit `i` is one.  It is a Clifford involution.  Define

```text
P_B(u)=P(u),
Q_B(v)=Q(B_0 v) product_i CZ_i(B_i v).                 (ACP3)
```

On the joint `Z`-selector sector `x`, `(ACP3)` is exactly

```text
P_B(u)=P(u),                 Q_B(v)=Q(B(x)v),           (ACP4)
```

so

```text
[P_B(u),Q_B(v)]
 =J^(u^T B_0 v) product_i Z_i^(u^T B_i v).             (ACP5)
```

Thus all sixteen nondegenerate residual forms occur in one ordinary finite
Clifford multiplication table, on one rank-fifteen residual spin factor.  The
dummy qubit does not occur in `(ACP3)--(ACP8)`.  Consequently every full
four-bit semantic selector character, not merely every value of one reset
sign, has carrier

```text
rho_15 tensor C^2_dummy = 2 rho_15.                    (ACP4')
```

This inert factor is essential: with only nineteen qubits, fixing all four
semantic selector signs leaves a one-dimensional selector sector and there
is no two-dimensional spin left for the rank swap.

For a nonzero gauge direction `a in F_2^4`, put

```text
T_a=product_i X_i^(a_i).                               (ACP6)
```

Then

```text
T_a Z_i T_a^(-1)=J^(a_i) Z_i,                          (ACP7)
```

and conjugating `(ACP3)` multiplies `Q_B(v)` by the residual derivative word

```text
Q((sum_i a_i B_i)v).                                   (ACP8)
```

Equations `(ACP7)--(ACP8)` are exactly the gauge-selector translation and
Weyl derivative reset.  The logical products of gauge-doubled BCS shares are
fixed because both shares translate together.

Let `C_20` be the full finite phase-extended Clifford group on these twenty
qubits.  It contains the Pauli group, all controlled operators in `(ACP3)`,
and every selector Clifford change of basis used by the reset packet.  The
Pauli subgroup has a unique irreducible `J=-1` spin type.  Consequently the
restriction of **every** `J=-1` representation of `C_20` to the Pauli
subgroup is

```text
rho_20 tensor I_M,                                      (ACP9)
```

for one arbitrary common multiplicity space `M`.  Every semantic selector
sector in `(ACP4')` therefore has the same residual and dummy-spin
multiplicity.  Different Clifford extension types can only decompose the
common factor `M`; they cannot create a new selector-dependent mode.

Finite-group Hilbert--Schmidt exactification of the complete table of `C_20`
therefore gives a dimension-independent robust version of `(ACP3)--(ACP9)`
on the entire relevant `J=-1` carrier, not merely one primitive summand.
