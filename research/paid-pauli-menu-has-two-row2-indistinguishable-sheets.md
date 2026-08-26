---
rg: 2
id: paid-pauli-menu-has-two-row2-indistinguishable-sheets
kind: claim
title: The eight paid Pauli conjugates collapse to two row-two-indistinguishable sheets
artifacts:
  - research/paid-pauli-menu-row2-sheet-fence-proof.md
distinct_from:
  paid-t00-pauli-menu-hits-whitehead-constant-atom: that averages the paid discrepancy onto the equal-scale Whitehead constant atom; this computes every menu word against the actual row-two arms and shows that the unequal quarter/eighth typing is still absent.
  native-t00-collision-first-hecke-attachment-has-gl10-model: that tests the single mixed commutator with B_2 and has no Pauli atom menu; this shows that all eight menu words give the same B_2 attachment up to an invisible two-sheet factor.
  paid-t00-carrier-can-miss-row2-source: that separates one fixed signed source from the paid carrier in a reducible model; this gives the smaller literal reason the Pauli menu itself cannot choose a row-two sheet, before any signed Reynolds projection is introduced.
---

**ESTABLISHED TWO-SHEET OCCURRENCE FENCE.**  Retain the paid root and the
three literal middle-index Pauli flips

```text
D=x_78(d),                 d=(1+s_0)t_00,
Y_m=x_(k_m,3)(b_m),        (k_1,k_2,k_3)=(7,8,9),
b_m=s_(0^m)t_1.                                      (P2S1)
```

For the eight words `u_epsilon` used in
`paid-t00-pauli-menu-hits-whitehead-constant-atom`, let `eta(epsilon)` be
the parity with which `Y_2` occurs.  Direct ordinary-root collection gives

```text
H=[D,Y_2]=x_73(h),          h=db_2=t_1+s_0t_1,
D_epsilon=u_epsilon^(-1)Du_epsilon
         =D H^(eta(epsilon)).                         (P2S2)
```

Indeed `Y_1` and `Y_3` commute with `D`, and all three `Y_m` commute with
one another.  Thus the advertised eight-word menu consists of four copies
of `D` and four copies of `DH` (or fewer values only after a representation
kills `H`).  The averaging result remains fully valid, but it is an
equal-scale constant-atom localization; it does not produce eight
different candidates for the unequal selector row.

Now insert the actual row-two occurrences

```text
T=x_78(t_00),       A_2=x_58(a_2),
B_2=x_84(b_2),      B_3=x_95(b_3),
J_2=x_98(x_2)x_89(y_2)x_98(x_2),
M_2=J_2B_3A_2,      M_2^7=1.                         (P2S3)
```

The root positions alone give

```text
[H,T]=[H,A_2]=[H,B_2]=[H,B_3]=[H,J_2]=1.             (P2S4)
```

Consequently every named ordinary test in this row is blind to the sheet:

```text
[D_epsilon,T]=[D_epsilon,A_2]=[D_epsilon,B_3]=1,
[D_epsilon,B_2]=[D,B_2]=x_74(h),                     (P2S5)

J_2^(-1)D_epsilon J_2=(J_2^(-1)DJ_2)H^(eta(epsilon)),
M_2^(-k)D_epsilon M_2^k=(M_2^(-k)DM_2^k)H^(eta(epsilon)).
                                                               (P2S6)
```

In particular the order-seven orbit returns after seven steps with the same
unchanged `H`-sheet.  The odd head authenticates `J_2` against `B_3A_2`,
but it neither kills `H` nor selects one of `D,DH` as a controlled
one-eighth output.  The first Hecke attachment through `B_2` is also
identical on the two sheets.

This invariance has a small exact marked fence.  On
`(C^2)^(tensor 4)` take the three standard Pauli pairs on the first three
qubits, center `z=-I`, and

```text
D=-Z_2,          H=-I,          Y_2=X_2,          T=DY_1.  (P2S7)
```

Then `Y_2DY_2=DH`; the other two Pauli flips commute with `D`.  With the
`X`-character convention of `(PAM1)`, the constant atom has dimension two
and exactly one of the two sheets has paid compression on it.  Adjacent
tensor swaps realize the two literal Whiteheads and preserve that atom.
Set

```text
J_1=B_2=SWAP_(1,2),
J_2=SWAP_(2,3),       A_2=CNOT_(2->4),
B_3=CNOT_(4->3).                                      (P2S8)
```

On the three binary coordinates `(4,2,3)` these are exactly the matrices
`A,B,J` of `(OWH7)`, so `(J_2B_3A_2)^7=1`; `A_2,B_3` commute with both
`D` and `T`.  The native path `[S_57,T]=A_2` is also exact: with
`P_-=(1-A_2)/2`, take `S_57=(1-P_-)+Z_1P_-`.  The `A_2=-1` sector has
balanced `T` signs, and direct multiplication gives the commutator `A_2`.
Thus `T,A_2,B_2,B_3,J_2` are all nontrivial in this sixteen-dimensional
model while the paid menu still has only its invisible two sheets.  The
fourth qubit is precisely the extra coordinate needed by this literal
noncollapsed order-seven triangle; no direct-sum segregation is being used.

This is a scoped exact finite model of the currently named Pauli-menu and
row-two occurrence table, not a representation of the full binary-Leavitt
elementary or Steinberg group.  It does not rule out a larger ordinary word
that fails to commute with `H`, nor a source-incidence row forced by the
full presentation.  It proves only the required sharp boundary: none of
`T,A_2,B_2,B_3,J_2` or the order-seven head, with the relations presently
named, upgrades the equal-scale Whitehead constant-atom payment to the
actual quarter/eighth controlled selector row.  A successful continuation
must contain an ordinary occurrence which detects `H` or places one sheet
on the authenticated unequal source carrier.  No Property T, canonical
trace, literature input, local computation, or Lean compilation is used.

DERIVATION
paid-pauli-menu-row2-sheet-fence-proof
