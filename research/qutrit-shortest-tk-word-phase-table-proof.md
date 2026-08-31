---
rg: 2
id: qutrit-shortest-tk-word-phase-table-proof
kind: proof
title: Compare the seven dihedral matrices with the affine qutrit stabilizers
target: qutrit-shortest-tk-word-graphs-are-diagonal-or-complete
requires:
  - qutrit-scalar-opposite-root-is-diagonal-or-complete
  - jacobson-pre-reduction-square-forces-sqrt-half-leakage
---

Work in the active three-coordinate block. Direct multiplication gives

| word | active matrix | required fixed coordinates |
|---|---|---|
| `k` | `I+E_31` | `1,3` |
| `t` | `I+T E_23` | `2,3` |
| `u=(tk)^2` | `I+T E_21` | `1,2` |
| `ktk` | `I+T(E_23+E_21)` | `1,2,3` |
| `tkt` | `I+E_31+T E_21` | `1,2,3` |
| `kt` | `I+E_31+T E_23` | `1,2,3` |
| `tk` | `I+E_31+T(E_23+E_21)` | `1,2,3` |

Here the last column has the following exact meaning. If `P` is a
permutation matrix of an element of `C`, then

```text
gPg^(-1) is a scalar permutation matrix
if and only if P fixes every listed coordinate.          (QDW2)
```

For `k`, this is the scalar transvection calculation from the
prerequisite. For a raw root `I+T E_ij`, expansion gives

```text
(I+T E_ij)P(I+T E_ij)
 =P+T(E_ijP+PE_ij)+T^2E_ijPE_ij.
```

The Jacobson normal forms `1,T,T^2` are linearly independent. Vanishing
of the two non-scalar coefficients is equivalent to `P` fixing `i,j`.
This proves the rows for `t` and `u`.

For the remaining rows, abbreviate

```text
A=E_31,       B=E_23,       C_0=E_21,       D=B+C_0.
```

For `ktk=I+TD`, comparison of the `T`-coefficient says that `P`
commutes with `D=e_2(e_1^*+e_3^*)`. Thus it fixes coordinate `2` and
preserves the set `{1,3}`. Every element of the odd-order group `C`
has odd order, so it cannot swap two coordinates and must fix both.

For each of `tkt`, `kt`, and `tk`, the scalar coefficient of
`gPg^(-1)` is

```text
(I+A)P(I+A).
```

The scalar transvection calculation first forces `P` to fix coordinates
`1,3`, after which `P` commutes with `A`. The remaining
`T`-coefficient reduces respectively to

```text
C_0P+PC_0,          DP+PD,          BP+PB.
```

Its vanishing forces coordinate `2` to be fixed as well; the
`T^2`-coefficient then vanishes automatically. Conversely a permutation
fixing the listed coordinates commutes with the displayed matrix. This
proves `(QDW2)`.

If `c in C intersect gCg^(-1)`, write `c=gc'g^(-1)` with
`c' in C`. Both sides are scalar permutation matrices, so `(QDW2)`
forces `c'` to fix the listed coordinates. It then commutes with `g`
and `c=c'`. Therefore `H_g` is exactly the corresponding common
point stabilizer.

The explicit qutrit action is

```text
J^aZ_1^b:(u_1,u_2,s) |-> (u_1,u_2,s+a-bu_1).
```

A leaf stabilizer is the order-three group
`{J^(bu_1)Z_1^b:b in F_3}`. Intersecting the stabilizers in any row of
the table gives either that group, when all relevant leaf coordinates have
one `u_1`-value, or the identity, when two values differ. The extra
coordinate is fixed by `C` and imposes no further condition. Thus
`|H_g|` is always `1` or `3`.

Finally, finite-group character intertwining gives

```text
e_b g e_a=0 unless chi_a|_(H_g)=chi_b|_(H_g),
||e_b g e_a||_2^2=|H_g|/81 when the restrictions agree. (QDW3)
```

For a nontrivial point stabilizer the three restrictions are distinct,
whereas for the trivial group all agree. Substitution in `(QDW3)` proves
`(QDW1)` and completes the bounded-word exhaustion.
