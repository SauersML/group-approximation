---
rg: 2
id: paid-pauli-menu-row2-sheet-fence-proof
kind: route
title: Collect the paid menu and isolate its row-two-invisible sheet root
target: paid-pauli-menu-has-two-row2-indistinguishable-sheets
requires:
  - paid-t00-pauli-menu-hits-whitehead-constant-atom
  - native-t00-y1-collision-pays-marked-opnorm
  - native-whitehead-hecke-head-has-order-seven-anchor
  - prefix-order-seven-pair-retains-gl7-mark
---

Write `D=x_78(d)` with `d=(1+s_0)t_00`.  Among the three menu flips only
`Y_2=x_83(b_2)` is incident to `(7,8)`.  Characteristic-two elementary
collection therefore gives

```text
Y_2 D Y_2=D x_73(db_2),
db_2=(1+s_0)t_00s_00t_1=t_1+s_0t_1.                  (1)
```

The other two flips have positions `(7,3)` and `(9,3)`: the first shares
the initial index with `D` and the second is nonincident, so both commute
with `D`.  All three flips share the terminal index `3` and commute
pairwise.  Equation `(1)` proves `(P2S2)` and the four-plus-four menu count.

Put `H=x_73(t_1+s_0t_1)`.  Its position `(7,3)` is nonincident to
`(5,8)`, `(8,4)`, `(9,5)`, `(9,8)`, and `(8,9)`, and it shares only an
initial index with `T=x_78(t_00)`.  This proves `(P2S4)`.  The same
root-position check gives the first line of `(P2S5)`, while

```text
[D,B_2]=x_74(db_2)=x_74(t_1+s_0t_1).                 (2)
```

Since `H` commutes with `B_2`, equation `(2)` is unchanged after replacing
`D` by `DH`.  Since it also commutes with every factor of `J_2`, with
`A_2`, and with `B_3`, it commutes with `M_2=J_2B_3A_2`; conjugation gives
`(P2S6)` for every integer `k`.  Taking `k=7` and using `M_2^7=1` shows
that the odd head returns each sheet to itself rather than comparing the
two sheets.

For the finite fence use four qubits, with the standard three-qubit Pauli
representation on the first three: group-theoretic `X_m=Z_m`, `Y_m=X_m`
and central commutator `z=-I`.
Set `D=-Z_2` and `T=DY_1`.  Then `D=TY_1`, the `Y_2` conjugate is
`Z_2=D(-I)`, and `Y_1,Y_3` commute with `D`.  The constant joint `+1`
eigenspace of the three `Z_m` has dimension two and lies in the negative
eigenspace of `D`, whereas it
lies in the positive eigenspace of `DH`; hence the paid localization is
realized and does not choose an unequal row type.  The adjacent qubit swaps
give the literal Whitehead action.  Put

```text
J_1=B_2=SWAP_(1,2),       J_2=SWAP_(2,3),
A_2=CNOT_(2->4),           B_3=CNOT_(4->3).            (3)
```

The braid is exact.  On the three coordinates `(4,2,3)`, the last three
operators are the literal `A,B,J` matrices in `(OWH7)`, so the second head
has order seven.  Both `A_2` and `B_3` commute with `D` and `T`.  Map the
mixed output `x_74(h)` to the actual commutator
`[D,B_2]`; it is unchanged after replacing `D` by the scalar translate
`DH`.  This explicitly realizes every relation used in `(P2S4)--(P2S6)`.

Finally let `P_-=(1-A_2)/2` and
`S_57=(1-P_-)+Z_1P_-`.  Since `Z_1` commutes with `A_2` and anticommutes
with `T` exactly on the `A_2=-1` sector, `S_57` is an involution and
`[S_57,T]=A_2`.  Hence the literal `T` factorization of the actual row-two
arm is retained rather than segregated into another summand.  All five
named row-two operators are nonidentity.  This sixteen-dimensional block
is the smallest literal Pauli/permutation construction found here: eight
dimensions carry the required `M_8(C)` label, and one extra binary
coordinate carries the noncollapsed `GL_3(F_2)` order-seven triangle while
leaving `T,D` fixed.
